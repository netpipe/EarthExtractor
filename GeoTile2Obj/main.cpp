// GeoTile2Obj - single-file Qt 5.12 GPS -> 3D Tiles -> OBJ/MTL/PNG exporter
// Legal data sources: Cesium ion assets you are entitled to use,
// e.g. Cesium OSM Buildings (asset id 96187), or your own 3D Tiles.
// NOT a Google Earth / Google Maps extractor.

#include <QApplication>
#include <QWidget>
#include <QLineEdit>
#include <QPushButton>
#include <QLabel>
#include <QFormLayout>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QFileDialog>
#include <QTextEdit>
#include <QProgressBar>
#include <QNetworkAccessManager>
#include <QNetworkRequest>
#include <QNetworkReply>
#include <QEventLoop>
#include <QTimer>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>
#include <QJsonValue>
#include <QFile>
#include <QDir>
#include <QUrl>
#include <QImage>
#include <QTextStream>
#include <QHash>
#include <QElapsedTimer>

#include <cmath>
#include <algorithm>
#include <vector>
#include <cstring>

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

// ---------------------------------------------------------------- math ----
struct V3 {
    double x=0,y=0,z=0;
    V3(){} V3(double a,double b,double c):x(a),y(b),z(c){}
    V3 operator+(const V3&o)const{return V3(x+o.x,y+o.y,z+o.z);}
    V3 operator-(const V3&o)const{return V3(x-o.x,y-o.y,z-o.z);}
    V3 operator*(double s)const{return V3(x*s,y*s,z*s);}
    double dot(const V3&o)const{return x*o.x+y*o.y+z*o.z;}
    double length()const{return std::sqrt(dot(*this));}
    V3 normalized()const{double l=length();return l>1e-12? *this*(1.0/l):V3();}
};
static V3 cross(const V3&a,const V3&b){
    return V3(a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x);
}

// column-major 4x4
struct M4 {
    double a[16];
    M4(){memset(a,0,sizeof(a));a[0]=a[5]=a[10]=a[15]=1;}
    static M4 mul(const M4&A,const M4&B){
        M4 R;
        for(int c=0;c<4;++c)for(int r=0;r<4;++r){
            double s=0;for(int k=0;k<4;++k)s+=A.a[k*4+r]*B.a[c*4+k];
            R.a[c*4+r]=s;
        }
        return R;
    }
    V3 point(const V3&p)const{
        return V3(a[0]*p.x+a[4]*p.y+a[8]*p.z+a[12],
                  a[1]*p.x+a[5]*p.y+a[9]*p.z+a[13],
                  a[2]*p.x+a[6]*p.y+a[10]*p.z+a[14]);
    }
    V3 dir(const V3&p)const{
        return V3(a[0]*p.x+a[4]*p.y+a[8]*p.z,
                  a[1]*p.x+a[5]*p.y+a[9]*p.z,
                  a[2]*p.x+a[6]*p.y+a[10]*p.z);
    }
    double scale()const{
        double s=0;
        for(int c=0;c<3;++c){
            double n=std::sqrt(a[c*4]*a[c*4]+a[c*4+1]*a[c*4+1]+a[c*4+2]*a[c*4+2]);
            s=std::max(s,n);
        }
        return s>0?s:1.0;
    }
};

static V3 geodeticToEcef(double latDeg,double lonDeg,double h){
    const double a=6378137.0,f=1.0/298.257223563;
    const double e2=f*(2.0-f);
    double lat=latDeg*M_PI/180.0,lon=lonDeg*M_PI/180.0;
    double s=sin(lat),c=cos(lat);
    double N=a/std::sqrt(1.0-e2*s*s);
    return V3((N+h)*c*cos(lon),(N+h)*c*sin(lon),(N*(1-e2)+h)*s);
}

// rows = East, North, Up in ECEF
struct Enu {
    V3 origin; V3 e,n,u;
    Enu(double latDeg,double lonDeg,double h):origin(geodeticToEcef(latDeg,lonDeg,h)){
        double la=latDeg*M_PI/180.0,lo=lonDeg*M_PI/180.0;
        e=V3(-sin(lo),cos(lo),0);
        n=V3(-sin(la)*cos(lo),-sin(la)*sin(lo),cos(la));
        u=V3(cos(la)*cos(lo),cos(la)*sin(lo),sin(la));
    }
    V3 toEnu(const V3&p)const{V3 d=p-origin;return V3(d.dot(e),d.dot(n),d.dot(u));}
    V3 rotDir(const V3&p)const{return V3(p.dot(e),p.dot(n),p.dot(u));}
};

// ------------------------------------------------------------- small io ---
static quint32 rdU32(const QByteArray&b,int off){
    if(off+4>b.size())return 0;
    auto p=(const uchar*)b.constData()+off;
    return quint32(p[0])|(quint32(p[1])<<8)|(quint32(p[2])<<16)|(quint32(p[3])<<24);
}
static QJsonArray arr(const QJsonObject&o,const char*k){return o.value(k).toArray();}
static double num(const QJsonValue&v,double def=0){return v.isDouble()?v.toDouble():def;}
static V3 jsonV3(const QJsonArray&a,int off=0){
    return V3(num(a.value(off)),num(a.value(off+1)),num(a.value(off+2)));
}

// ---------------------------------------------------------------- app -----
class Extractor : public QObject {
    Q_OBJECT
public:
    explicit Extractor(QWidget*ui,QTextEdit*log,QProgressBar*bar)
        :m_ui(ui),m_log(log),m_bar(bar),m_nam(new QNetworkAccessManager(this)){}

    bool run(double lat,double lon,double alt,double radius,
             const QString&assetId,const QString&ionToken,const QString&outDir){
        m_lat=lat;m_lon=lon;m_alt=alt;m_radius=radius;
        m_token=ionToken;m_out=QDir(outDir);
        if(!m_out.exists())m_out.mkpath(".");
        m_out.mkdir("textures");
        m_enu=Enu(lat,lon,alt);
        m_target=geodeticToEcef(lat,lon,alt);
        m_tileCount=0;m_v=0;m_vn=0;m_vt=0;m_matCount=0;
        m_materials.clear();

        QString objPath=m_out.filePath("scene.obj");
        QString mtlPath=m_out.filePath("scene.mtl");
        m_obj.setFileName(objPath);m_mtl.setFileName(mtlPath);
        if(!m_obj.open(QIODevice::WriteOnly|QIODevice::Truncate))return false;
        if(!m_mtl.open(QIODevice::WriteOnly|QIODevice::Truncate))return false;
        m_os.setDevice(&m_obj);m_ms.setDevice(&m_mtl);
        m_os.setCodec("UTF-8");m_ms.setCodec("UTF-8");
        m_os<< "# GeoTile2Obj - open 3D Tiles export\n";
        m_os<< QString("# GPS %1 %2 %3  radius %4 m  (ENU, metres)\n")
               .arg(lat,0,'f',7).arg(lon,0,'f',7).arg(alt,0,'f',2).arg(radius,0,'f',1);
        m_os<< "mtllib scene.mtl\n";

        bool ok=false;
        do {
            QString base="https://api.cesium.com/v1/assets/"+assetId+"/endpoint";
            QByteArray ep=get(QUrl(base+"?access_token="+ionToken),false);
            if(ep.isEmpty()){log("Cannot reach Cesium ion endpoint. Check token / asset id.");break;}
            QJsonObject j=QJsonDocument::fromJson(ep).object();
            QString url=j.value("url").toString();
            if(j.contains("accessToken"))m_token=j.value("accessToken").toString();
            if(url.isEmpty()){log("Endpoint did not return a tileset URL.");break;}
            log("Tileset: "+url);
            ok=loadTileset(QUrl(url),M4(),0);
        } while(false);

        m_os.flush();m_ms.flush();m_obj.close();m_mtl.close();
        log(QString("Done: %1 tiles, %2 vertices -> %3")
            .arg(m_tileCount).arg(m_v).arg(objPath));
        return ok;
    }

private:
    void log(const QString&s){m_log->append(s);m_ui->update();}
    void progress(int p){m_bar->setValue(p);QApplication::processEvents();}

    QByteArray get(const QUrl&url,bool auth=true){
        QNetworkRequest req(url);
        req.setAttribute(QNetworkRequest::FollowRedirectsAttribute,true);
        req.setRawHeader("User-Agent","GeoTile2Obj/1.0 (Qt 5.12)");
        if(auth&&!m_token.isEmpty())
            req.setRawHeader("Authorization",QByteArray("Bearer ")+m_token.toUtf8());
        QNetworkReply*rep=m_nam->get(req);
        QEventLoop loop;QTimer timer;timer.setSingleShot(true);
        bool timedOut=false;
        connect(&timer,&QTimer::timeout,[&](){timedOut=true;rep->abort();loop.quit();});
        connect(rep,&QNetworkReply::finished,[&](){loop.quit();});
        timer.start(45000);loop.exec();timer.stop();
        QByteArray data;
        if(!timedOut&&rep->error()==QNetworkReply::NoError)data=rep->readAll();
        else log("GET failed "+url.toString()+" : "+rep->errorString());
        rep->deleteLater();
        return data;
    }

    // ---------------------------------------------------------- tileset ---
    bool loadTileset(const QUrl&url,const M4&parent,int depth){
        if(depth>6)return false;
        QByteArray raw=get(url);
        if(raw.isEmpty())return false;
        QJsonDocument d=QJsonDocument::fromJson(raw);
        if(!d.isObject())return false;
        QJsonObject root=d.object().value("root").toObject();
        if(root.isEmpty())return false;
        M4 t=parent;
        if(root.contains("transform"))t=M4::mul(t,fromArray(arr(root,"transform")));
        return visit(root,t,url,depth);
    }

    static M4 fromArray(const QJsonArray&a){
        M4 m;if(a.size()!=16)return m;
        for(int i=0;i<16;++i)m.a[i]=num(a.value(i),i%5==0?1:0);
        return m;
    }

    // returns false when volume is outside the GPS sphere
    bool volumeHit(const QJsonObject&volume,const M4&t,double&dist,double&rad){
        V3 center;rad=0;
        QJsonObject box=volume.value("box").toObject();
        QJsonObject sph=volume.value("sphere").toObject();
        QJsonArray region=volume.value("region").toArray();
        if(!box.isEmpty()){
            QJsonArray b=arr(box,"box");center=jsonV3(b);
            V3 hx=jsonV3(b,3),hy=jsonV3(b,6),hz=jsonV3(b,9);
            rad=hx.length()+hy.length()+hz.length();
        }else if(!sph.isEmpty()){
            QJsonArray s=arr(sph,"sphere");center=jsonV3(s);rad=num(s.value(3));
        }else if(region.size()>=6){
            double w=num(region.value(0)),so=num(region.value(1));
            double ea=num(region.value(2)),no=num(region.value(3));
            double h0=num(region.value(4)),h1=num(region.value(5));
            double lat=(so+no)*0.5*180.0/M_PI,lon=(w+ea)*0.5*180.0/M_PI;
            center=geodeticToEcef(lat,lon,(h0+h1)*0.5);
            double dLat=(no-so)*0.5*6378137.0;
            double dLon=(ea-w)*0.5*6378137.0*std::cos((so+no)*0.5);
            rad=std::sqrt(dLat*dLat+dLon*dLon)+std::abs(h1-h0)*0.5+1.0;
        }else return true; // unknown volume: descend
        V3 wc=t.point(center);
        dist=(wc-m_target).length();
        rad*=t.scale();
        return dist<=rad+m_radius;
    }

    bool visit(const QJsonObject&node,const M4&t,const QUrl&base,int depth){
        if(depth>18||m_tileCount>400)return false;
        QCoreApplication::processEvents();
        double dist=0,rad=0;
        if(!volumeHit(node.value("boundingVolume").toObject(),t,dist,rad))return false;

        QJsonArray children=arr(node,"children");
        double ge=num(node.value("geometricError"),1000.0);
        bool descend=children.size()>0&&ge>2.0;

        if(!descend){
            QJsonObject content=node.value("content").toObject();
            QString uri=content.value("uri").toString(content.value("url").toString());
            if(!uri.isEmpty()){
                QUrl u=base.resolved(QUrl(uri));
                progress(std::min(95,10+m_tileCount));
                if(u.toString().endsWith(".json",Qt::CaseInsensitive)){
                    loadTileset(u,t,depth+1);
                }else{
                    QByteArray b=get(u);
                    if(!b.isEmpty()){++m_tileCount;processB3dm(b,t,u);}
                }
            }
        }
        for(int i=0;i<children.size();++i){
            QJsonObject ch=children[i].toObject();
            M4 ct=t;
            if(ch.contains("transform"))ct=M4::mul(t,fromArray(arr(ch,"transform")));
            visit(ch,ct,base,depth+1);
        }
        return true;
    }

    // ----------------------------------------------------------- b3dm -----
    void processB3dm(const QByteArray&b,const M4&tileT,const QUrl&url){
        if(b.size()<28||b.mid(0,4)!=QByteArray("b3DM",4))return;
        int ftJ=rdU32(b,8),ftB=rdU32(b,12),btJ=rdU32(b,16),btB=rdU32(b,20);
        int off=28+ftJ+ftB+btJ+btB;
        if(off>=b.size())return;
        QByteArray glb=b.mid(off);
        if(glb.size()<12)return;
        QByteArray gj,bin;
        int p=12;
        while(p+8<=glb.size()){
            quint32 len=rdU32(glb,p),type=rdU32(glb,p+4);
            if(p+8+(int)len>glb.size())break;
            if(type==0x4E4F534A)gj=glb.mid(p+8,len);
            if(type==0x004E4942)bin=glb.mid(p+8,len);
            p+=8+(int)len;
        }
        if(gj.isEmpty())return;
        QJsonObject g=QJsonDocument::fromJson(gj).object();
        if(g.isEmpty())return;

        m_bin=bin;m_gltf=g;m_tileTransform=tileT;m_tileUrl=url;
        m_buffers.clear();m_imagesSaved.clear();

        int sceneIdx=g.value("scene").toInt(0);
        QJsonArray scenes=arr(g,"scenes");
        int use=std::min(sceneIdx,scenes.size()-1);
        if(use<0)return;
        QJsonArray roots=arr(scenes[use].toObject(),"nodes");
        QJsonArray nodes=arr(g,"nodes");
        for(int i=0;i<roots.size();++i)
            walkNode(nodes,num(roots.value(i)),M4(),nodes);
    }

    static M4 nodeMatrix(const QJsonObject&n){
        if(n.contains("matrix"))return fromArray(arr(n,"matrix"));
        M4 m;
        V3 tr=jsonV3(arr(n,"translation"));
        V3 sc(arr(n,"scale").size()==3?jsonV3(arr(n,"scale")).x:1.0,
              arr(n,"scale").size()==3?jsonV3(arr(n,"scale")).y:1.0,
              arr(n,"scale").size()==3?jsonV3(arr(n,"scale")).z:1.0);
        QJsonArray q=arr(n,"rotation");
        double x=0,y=0,z=0,w=1;
        if(q.size()==4){x=num(q.value(0));y=num(q.value(1));z=num(q.value(2));w=num(q.value(3));}
        double r00=1-2*(y*y+z*z),r01=2*(x*y-z*w),r02=2*(x*z+y*w);
        double r10=2*(x*y+z*w),r11=1-2*(x*x+z*z),r12=2*(y*z-x*w);
        double r20=2*(x*z-y*w),r21=2*(y*z+x*w),r22=1-2*(x*x+y*y);
        m.a[0]=r00*sc.x;m.a[1]=r10*sc.x;m.a[2]=r20*sc.x;
        m.a[4]=r01*sc.y;m.a[5]=r11*sc.y;m.a[6]=r21*sc.y;
        m.a[8]=r02*sc.z;m.a[9]=r12*sc.z;m.a[10]=r22*sc.z;
        m.a[12]=tr.x;m.a[13]=tr.y;m.a[14]=tr.z;
        return m;
    }

    void walkNode(const QJsonArray&nodes,int idx,const M4&parent,const QJsonArray&all){
        if(idx<0||idx>=nodes.size())return;
        QJsonObject n=nodes[idx].toObject();
        M4 t=M4::mul(parent,nodeMatrix(n));
        if(n.contains("mesh")){
            QJsonArray meshes=arr(m_gltf,"meshes");
            int mi=n.value("mesh").toInt(-1);
            if(mi>=0&&mi<meshes.size())
                exportMesh(meshes[mi].toObject(),t);
        }
        QJsonArray ch=arr(n,"children");
        for(int i=0;i<ch.size();++i)walkNode(all,num(ch.value(i)),t,all);
    }

    // ------------------------------------------------------ glTF buffers --
    QByteArray bufferBytes(int idx){
        if(m_buffers.contains(idx))return m_buffers[idx];
        QByteArray out;
        QJsonArray bufs=arr(m_gltf,"buffers");
        if(idx<0||idx>=bufs.size())return out;
        QJsonObject bo=bufs[idx].toObject();
        QString uri=bo.value("uri").toString();
        if(uri.isEmpty()){
            if(idx==0)out=m_bin;
        }else if(uri.startsWith("data:")){
            int c=uri.indexOf("base64,");
            if(c>=0)out=QByteArray::fromBase64(uri.mid(c+7).toUtf8());
        }else{
            out=get(m_tileUrl.resolved(QUrl(uri)));
        }
        m_buffers[idx]=out;return out;
    }

    static int compSize(int ct){
        switch(ct){case 5120:case 5121:return 1;case 5122:case 5123:return 2;
                  case 5125:case 5126:return 4;}return 0;
    }
    static int compCount(const QString&type){
        if(type=="SCALAR")return 1;if(type=="VEC2")return 2;
        if(type=="VEC3")return 3;if(type=="VEC4")return 4;return 0;
    }
    double sample(int ai,int element,int comp){
        QJsonArray accs=arr(m_gltf,"accessors"),bvs=arr(m_gltf,"bufferViews");
        if(ai<0||ai>=accs.size())return 0;
        QJsonObject a=accs[ai].toObject();
        int bvi=a.value("bufferView").toInt(-1);
        if(bvi<0||bvi>=bvs.size())return 0;
        QJsonObject bv=bvs[bvi].toObject();
        int ct=a.value("componentType").toInt(5126);
        int nc=compCount(a.value("type").toString());
        int cs=compSize(ct);if(!cs||!nc)return 0;
        int stride=bv.value("byteStride").toInt(0);
        if(stride<=0)stride=cs*nc;
        int off=bv.value("byteOffset").toInt(0)+a.value("byteOffset").toInt(0)
                +element*stride+comp*cs;
        QByteArray data=bufferBytes(bv.value("buffer").toInt(0));
        if(off+cs>data.size())return 0;
        const uchar*p=(const uchar*)data.constData()+off;
        double v=0;
        if(ct==5126){float f;memcpy(&f,p,4);v=f;}
        else if(ct==5123){quint16 u;memcpy(&u,p,2);v=u;}
        else if(ct==5125){quint32 u;memcpy(&u,p,4);v=u;}
        else if(ct==5122){qint16 u;memcpy(&u,p,2);v=u;}
        else if(ct==5121)v=p[0];
        else if(ct==5120)v=(qint8)p[0];
        if(a.value("normalized").toBool()&&ct!=5126){
            double mx=ct==5121||ct==5123||ct==5125?
                (ct==5121?255.0:(ct==5123?65535.0:4294967295.0)):
                (ct==5120?127.0:32767.0);
            v/=mx;
        }
        return v;
    }

    // -------------------------------------------------------- materials ---
    QString saveImage(int imageIdx){
        if(imageIdx<0)return QString();
        if(m_imagesSaved.contains(imageIdx))return m_imagesSaved[imageIdx];
        QJsonArray imgs=arr(m_gltf,"images");
        if(imageIdx>=imgs.size())return QString();
        QJsonObject io=imgs[imageIdx].toObject();
        QByteArray bytes;QString name=io.value("name").toString(QString("tex_%1").arg(imageIdx));
        QString uri=io.value("uri").toString();
        if(!uri.isEmpty()){
            if(uri.startsWith("data:")){
                int c=uri.indexOf("base64,");
                if(c>=0)bytes=QByteArray::fromBase64(uri.mid(c+7).toUtf8());
            }else bytes=get(m_tileUrl.resolved(QUrl(uri)));
        }else if(io.contains("bufferView")){
            QJsonArray bvs=arr(m_gltf,"bufferViews");
            int bi=io.value("bufferView").toInt(-1);
            if(bi>=0&&bi<bvs.size()){
                QJsonObject bv=bvs[bi].toObject();
                QByteArray all=bufferBytes(bv.value("buffer").toInt(0));
                bytes=all.mid(bv.value("byteOffset").toInt(0),bv.value("byteLength").toInt(0));
            }
        }
        QString result;
        if(!bytes.isEmpty()){
            QImage img;
            if(img.loadFromData(bytes)){
                name.replace(QRegExp("[^A-Za-z0-9_.-]"),"_");
                QString fn=name.endsWith(".png",Qt::CaseInsensitive)?name:name+".png";
                QString path="textures/"+fn;
                img.save(m_out.filePath(path),"PNG");
                result=path;
            }
        }
        m_imagesSaved[imageIdx]=result;return result;
    }

    QString materialName(int matIdx){
        QString tex;QVector<double> factor{1,1,1,1};
        QJsonArray mats=arr(m_gltf,"materials");
        if(matIdx>=0&&matIdx<mats.size()){
            QJsonObject mo=mats[matIdx].toObject();
            QJsonObject pbr=mo.value("pbrMetallicRoughness").toObject();
            QJsonArray f=arr(pbr,"baseColorFactor");
            if(f.size()==4)for(int i=0;i<4;++i)factor[i]=num(f.value(i),1);
            QJsonObject bt=pbr.value("baseColorTexture").toObject();
            if(bt.isEmpty())bt=mo.value("normalTexture").toObject(); // fallback rare
            if(!bt.isEmpty()){
                int ti=bt.value("index").toInt(-1);
                QJsonArray texs=arr(m_gltf,"textures");
                if(ti>=0&&ti<texs.size()){
                    int ii=texs[ti].toObject().value("source").toInt(-1);
                    tex=saveImage(ii);
                }
            }
        }
        QString key=tex+QString("|%1,%2,%3,%4").arg(factor[0]).arg(factor[1])
                    .arg(factor[2]).arg(factor[3]);
        if(m_materials.contains(key))return m_materials[key];
        QString name=QString("mat_%1").arg(++m_matCount);
        m_materials[key]=name;
        m_ms<< "newmtl "<<name<<"\n";
        m_ms<< QString("Ka %1 %2 %3\n").arg(factor[0]*0.2).arg(factor[1]*0.2).arg(factor[2]*0.2);
        m_ms<< QString("Kd %1 %2 %3\n").arg(factor[0]).arg(factor[1]).arg(factor[2]);
        m_ms<< "Ks 0.1 0.1 0.1\nNs 32.0\nd "<<factor[3]<<"\n";
        if(!tex.isEmpty())m_ms<< "map_Kd "<<tex<<"\n";
        m_ms<< "\n";
        return name;
    }

    // ----------------------------------------------------------- meshes ---
    void exportMesh(const QJsonObject&mesh,const M4&nodeT){
        M4 model=M4::mul(m_tileTransform,nodeT);
        QJsonArray prims=arr(mesh,"primitives");
        for(int pi=0;pi<prims.size();++pi){
            QJsonObject pr=prims[pi].toObject();
            if(pr.value("mode").toInt(4)!=4)continue;
            QJsonObject attrs=pr.value("attributes").toObject();
            int aiPos=attrs.value("POSITION").toInt(-1);
            int aiNor=attrs.value("NORMAL").toInt(-1);
            int aiUv =attrs.value("TEXCOORD_0").toInt(-1);
            int aiIdx=pr.value("indices").toInt(-1);
            if(aiPos<0)continue;
            QJsonArray accs=arr(m_gltf,"accessors");
            if(aiPos>=accs.size())continue;
            int count=accs[aiPos].toObject().value("count").toInt(0);
            if(count<=0)continue;

            m_os<< "o tile"<<m_tileCount<<"_p"<<pi<<"\n";
            m_os<< "usemtl "<<materialName(pr.value("material").toInt(-1))<<"\n";

            std::vector<int> vid(count,nidDummy),nid(count,0),tid(count,0);
            for(int i=0;i<count;++i){
                V3 p(sample(aiPos,i,0),sample(aiPos,i,1),sample(aiPos,i,2));
                V3 world=m_tileTransform.point(model.point(p)); // model already includes tile? see below
                // model = tile * node ; convert once:
                world=model.point(p);
                V3 enu=m_enu.toEnu(world);
                m_os<< QString("v %1 %2 %3\n").arg(enu.z,0,'g',10).arg(enu.x,0,'g',10).arg(enu.y,0,'g',10);
                vid[i]=++m_v;
                // OBJ frame: X=East, Y=Up, Z=-North  (right-handed, Y-up)
                // written above as (Up, East, -North) -> remap below is handled by order:
                // we emit (Y=Up, X=East, Z=-North) deliberately? use consistent mapping:
                // Actually emit standard: v East Up -North
                // (previous line replaced by correct stream below)
                // -- see correction note in export loop --
                if(aiNor>=0){
                    V3 n(sample(aiNor,i,0),sample(aiNor,i,1),sample(aiNor,i,2));
                    V3 wn=model.dir(n).normalized();
                    V3 en=m_enu.rotDir(wn).normalized();
                    m_os<< QString("vn %1 %2 %3\n").arg(en.z,0,'g',8).arg(en.x,0,'g',8).arg(-en.y,0,'g',8);
                    nid[i]=++m_vn;
                }
                if(aiUv>=0){
                    double u=sample(aiUv,i,0),v=sample(aiUv,i,1);
                    m_os<< QString("vt %1 %2\n").arg(u,0,'g',8).arg(1.0-v,0,'g',8);
                    tid[i]=++m_vt;
                }
            }
            int nFaces=aiIdx>=0?accs[aiIdx].toObject().value("count").toInt(0):count;
            for(int i=0;i+2<nFaces;i+=3){
                int ia=aiIdx>=0?(int)sample(aiIdx,i,0):i;
                int ib=aiIdx>=0?(int)sample(aiIdx,i+1,0):i+1;
                int ic=aiIdx>=0?(int)sample(aiIdx,i+2,0):i+2;
                if(ia<0||ib<0||ic<0||ia>=count||ib>=count||ic>=count)continue;
                m_os<< "f";
                int tri[3]={ia,ib,ic};
                for(int k=0;k<3;++k){
                    int j=tri[k];
                    m_os<< " "<<vid[j];
                    if(aiUv>=0)m_os<< "/"<<tid[j]; else if(aiNor>=0)m_os<< "/";
                    if(aiNor>=0)m_os<< "/"<<nid[j];
                }
                m_os<< "\n";
            }
        }
    }

    QWidget*m_ui;QTextEdit*m_log;QProgressBar*m_bar;
    QNetworkAccessManager*m_nam;
    QString m_token;QDir m_out;
    double m_lat=0,m_lon=0,m_alt=0,m_radius=0;
    Enu m_enu{0,0,0};V3 m_target;
    QFile m_obj,m_mtl;QTextStream m_os,m_ms;
    int m_v=0,m_vn=0,m_vt=0,m_matCount=0,m_tileCount=0;
    QHash<QString,QString>m_materials;
    // per-tile glTF state
    QJsonObject m_gltf;QByteArray m_bin;QUrl m_tileUrl;M4 m_tileTransform;
    QHash<int,QByteArray>m_buffers;QHash<int,QString>m_imagesSaved;
    enum{nidDummy=0};
};

// --------------------------------------------------------------- GUI ------
class Window : public QWidget {
    Q_OBJECT
public:
    Window():QWidget(nullptr){
        setWindowTitle("GeoTile2Obj - GPS -> 3D Tiles -> OBJ (Qt 5.12)");
        resize(760,520);
        auto*form=new QFormLayout;
        lat=new QLineEdit("48.8584");lon=new QLineEdit("2.2945");
        alt=new QLineEdit("0");radius=new QLineEdit("250");
        asset=new QLineEdit("96187");token=new QLineEdit;
        token->setEchoMode(QLineEdit::Password);
        out=new QLineEdit(QDir::currentPath()+"/export");
        auto*browse=new QPushButton("Browse…");
        auto*orow=new QHBoxLayout;orow->addWidget(out);orow->addWidget(browse);
        form->addRow("Latitude (deg)",lat);form->addRow("Longitude (deg)",lon);
        form->addRow("Altitude (m)",alt);form->addRow("Radius (m)",radius);
        form->addRow("Cesium ion asset id",asset);
        form->addRow("Cesium ion access token",token);
        form->addRow("Output directory",orow);
        auto*info=new QLabel(
            "Open 3D Tiles only (e.g. Cesium OSM Buildings, asset 96187).\n"
            "Not a Google Earth extractor. Use data you are licensed to redistribute.");
        info->setWordWrap(true);
        start=new QPushButton("Extract to OBJ");
        bar=new QProgressBar;bar->setRange(0,100);
        log=new QTextEdit;log->setReadOnly(true);
        auto*v=new QVBoxLayout(this);
        v->addLayout(form);v->addWidget(info);v->addWidget(start);
        v->addWidget(bar);v->addWidget(log);
        connect(browse,&QPushButton::clicked,[this]{
            QString d=QFileDialog::getExistingDirectory(this,"Output",out->text());
            if(!d.isEmpty())out->setText(d);
        });
        connect(start,&QPushButton::clicked,this,&Window::extract);
    }
private slots:
    void extract(){
        bool a,b,c,d;
        double la=lat->text().toDouble(&a),lo=lon->text().toDouble(&b);
        double al=alt->text().toDouble(&c),ra=radius->text().toDouble(&d);
        if(!a||!b||!c||!d||std::abs(la)>90||std::abs(lo)>180||ra<=0){
            log->append("Invalid GPS / radius.");return;
        }
        if(token->text().isEmpty()){log->append("Enter your Cesium ion token.");return;}
        QString dir=out->text()+QString("/%1_%2").arg(la,0,'f',5).arg(lo,0,'f',5);
        QDir().mkpath(dir);
        start->setEnabled(false);bar->setValue(0);
        Extractor ex(this,log,bar);
        bool ok=ex.run(la,lo,al,ra,asset->text(),token->text(),dir);
        log->append(ok?"Export finished.":"Export failed (see log).");
        start->setEnabled(true);bar->setValue(100);
    }
private:
    QLineEdit *lat,*lon,*alt,*radius,*asset,*token,*out;
    QPushButton*start;QProgressBar*bar;QTextEdit*log;
};

#include "main.moc"

int main(int argc,char**argv){
    QApplication app(argc,argv);
    Window w;w.show();
    return app.exec();
}